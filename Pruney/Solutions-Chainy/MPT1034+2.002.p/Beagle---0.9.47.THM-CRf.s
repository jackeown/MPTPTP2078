%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:57 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 147 expanded)
%              Number of leaves         :   20 (  61 expanded)
%              Depth                    :    6
%              Number of atoms          :  140 ( 530 expanded)
%              Number of equality atoms :    9 (  18 expanded)
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

tff(f_87,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_69,axiom,(
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

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_97,plain,(
    ! [A_36,B_37,C_38,D_39] :
      ( r2_relset_1(A_36,B_37,C_38,C_38)
      | ~ m1_subset_1(D_39,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [C_40] :
      ( r2_relset_1('#skF_1','#skF_1',C_40,C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_97])).

tff(c_112,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_106])).

tff(c_37,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( r2_relset_1(A_22,B_23,C_24,C_24)
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [C_26] :
      ( r2_relset_1('#skF_1','#skF_1',C_26,C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_22,c_37])).

tff(c_50,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_44])).

tff(c_27,plain,(
    ! [C_19,A_20,B_21] :
      ( v1_partfun1(C_19,A_20)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21)))
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_27])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_26,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_51,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_partfun1(C_27,A_28)
      | ~ v1_funct_2(C_27,A_28,B_29)
      | ~ v1_funct_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | v1_xboole_0(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_54,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_51])).

tff(c_60,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_54])).

tff(c_61,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_60])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_57,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_51])).

tff(c_64,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_57])).

tff(c_65,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_64])).

tff(c_14,plain,(
    r1_partfun1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_66,plain,(
    ! [D_30,C_31,A_32,B_33] :
      ( D_30 = C_31
      | ~ r1_partfun1(C_31,D_30)
      | ~ v1_partfun1(D_30,A_32)
      | ~ v1_partfun1(C_31,A_32)
      | ~ m1_subset_1(D_30,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_1(D_30)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_68,plain,(
    ! [A_32,B_33] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_32)
      | ~ v1_partfun1('#skF_2',A_32)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_66])).

tff(c_71,plain,(
    ! [A_32,B_33] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_32)
      | ~ v1_partfun1('#skF_2',A_32)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_68])).

tff(c_73,plain,(
    ! [A_34,B_35] :
      ( ~ v1_partfun1('#skF_3',A_34)
      | ~ v1_partfun1('#skF_2',A_34)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_76,plain,
    ( ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_61,c_65,c_76])).

tff(c_81,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_12,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_85,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_12])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_85])).

tff(c_95,plain,(
    v1_partfun1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_96,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_35,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_27])).

tff(c_105,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_35])).

tff(c_126,plain,(
    ! [D_44,C_45,A_46,B_47] :
      ( D_44 = C_45
      | ~ r1_partfun1(C_45,D_44)
      | ~ v1_partfun1(D_44,A_46)
      | ~ v1_partfun1(C_45,A_46)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_1(D_44)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_128,plain,(
    ! [A_46,B_47] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_46)
      | ~ v1_partfun1('#skF_2',A_46)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_126])).

tff(c_131,plain,(
    ! [A_46,B_47] :
      ( '#skF_2' = '#skF_3'
      | ~ v1_partfun1('#skF_3',A_46)
      | ~ v1_partfun1('#skF_2',A_46)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_20,c_128])).

tff(c_133,plain,(
    ! [A_48,B_49] :
      ( ~ v1_partfun1('#skF_3',A_48)
      | ~ v1_partfun1('#skF_2',A_48)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_136,plain,
    ( ~ v1_partfun1('#skF_3','#skF_1')
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_22,c_133])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_95,c_105,c_136])).

tff(c_141,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_145,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_12])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n010.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 13:01:29 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.29  
% 2.00/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.29  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.00/1.29  
% 2.00/1.29  %Foreground sorts:
% 2.00/1.29  
% 2.00/1.29  
% 2.00/1.29  %Background operators:
% 2.00/1.29  
% 2.00/1.29  
% 2.00/1.29  %Foreground operators:
% 2.00/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.29  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.00/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.00/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.00/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.00/1.29  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.00/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.29  
% 2.00/1.31  tff(f_87, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_funct_2)).
% 2.00/1.31  tff(f_31, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.00/1.31  tff(f_38, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 2.00/1.31  tff(f_52, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.00/1.31  tff(f_69, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 2.00/1.31  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.00/1.31  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.00/1.31  tff(c_97, plain, (![A_36, B_37, C_38, D_39]: (r2_relset_1(A_36, B_37, C_38, C_38) | ~m1_subset_1(D_39, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.31  tff(c_106, plain, (![C_40]: (r2_relset_1('#skF_1', '#skF_1', C_40, C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_97])).
% 2.00/1.31  tff(c_112, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_106])).
% 2.00/1.31  tff(c_37, plain, (![A_22, B_23, C_24, D_25]: (r2_relset_1(A_22, B_23, C_24, C_24) | ~m1_subset_1(D_25, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.31  tff(c_44, plain, (![C_26]: (r2_relset_1('#skF_1', '#skF_1', C_26, C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))))), inference(resolution, [status(thm)], [c_22, c_37])).
% 2.00/1.31  tff(c_50, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_44])).
% 2.00/1.31  tff(c_27, plain, (![C_19, A_20, B_21]: (v1_partfun1(C_19, A_20) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.00/1.31  tff(c_34, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_27])).
% 2.00/1.31  tff(c_36, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 2.00/1.31  tff(c_26, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.00/1.31  tff(c_24, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.00/1.31  tff(c_51, plain, (![C_27, A_28, B_29]: (v1_partfun1(C_27, A_28) | ~v1_funct_2(C_27, A_28, B_29) | ~v1_funct_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | v1_xboole_0(B_29))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.00/1.31  tff(c_54, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_51])).
% 2.00/1.31  tff(c_60, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_54])).
% 2.00/1.31  tff(c_61, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_60])).
% 2.00/1.31  tff(c_20, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.00/1.31  tff(c_18, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.00/1.31  tff(c_57, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_51])).
% 2.00/1.31  tff(c_64, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_57])).
% 2.00/1.31  tff(c_65, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_64])).
% 2.00/1.31  tff(c_14, plain, (r1_partfun1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.00/1.31  tff(c_66, plain, (![D_30, C_31, A_32, B_33]: (D_30=C_31 | ~r1_partfun1(C_31, D_30) | ~v1_partfun1(D_30, A_32) | ~v1_partfun1(C_31, A_32) | ~m1_subset_1(D_30, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_1(D_30) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_1(C_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.00/1.31  tff(c_68, plain, (![A_32, B_33]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_32) | ~v1_partfun1('#skF_2', A_32) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_66])).
% 2.00/1.31  tff(c_71, plain, (![A_32, B_33]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_32) | ~v1_partfun1('#skF_2', A_32) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_68])).
% 2.00/1.31  tff(c_73, plain, (![A_34, B_35]: (~v1_partfun1('#skF_3', A_34) | ~v1_partfun1('#skF_2', A_34) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(splitLeft, [status(thm)], [c_71])).
% 2.00/1.31  tff(c_76, plain, (~v1_partfun1('#skF_3', '#skF_1') | ~v1_partfun1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_22, c_73])).
% 2.00/1.31  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_61, c_65, c_76])).
% 2.00/1.31  tff(c_81, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_71])).
% 2.00/1.31  tff(c_12, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.00/1.31  tff(c_85, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_12])).
% 2.00/1.31  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_85])).
% 2.00/1.31  tff(c_95, plain, (v1_partfun1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.00/1.31  tff(c_96, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 2.00/1.31  tff(c_35, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_27])).
% 2.00/1.31  tff(c_105, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_35])).
% 2.00/1.31  tff(c_126, plain, (![D_44, C_45, A_46, B_47]: (D_44=C_45 | ~r1_partfun1(C_45, D_44) | ~v1_partfun1(D_44, A_46) | ~v1_partfun1(C_45, A_46) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_1(D_44) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_1(C_45))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.00/1.31  tff(c_128, plain, (![A_46, B_47]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_46) | ~v1_partfun1('#skF_2', A_46) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_126])).
% 2.00/1.31  tff(c_131, plain, (![A_46, B_47]: ('#skF_2'='#skF_3' | ~v1_partfun1('#skF_3', A_46) | ~v1_partfun1('#skF_2', A_46) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_20, c_128])).
% 2.00/1.31  tff(c_133, plain, (![A_48, B_49]: (~v1_partfun1('#skF_3', A_48) | ~v1_partfun1('#skF_2', A_48) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(splitLeft, [status(thm)], [c_131])).
% 2.00/1.31  tff(c_136, plain, (~v1_partfun1('#skF_3', '#skF_1') | ~v1_partfun1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_22, c_133])).
% 2.00/1.31  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_95, c_105, c_136])).
% 2.00/1.31  tff(c_141, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_131])).
% 2.00/1.31  tff(c_145, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_12])).
% 2.00/1.31  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_145])).
% 2.00/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.31  
% 2.00/1.31  Inference rules
% 2.00/1.31  ----------------------
% 2.00/1.31  #Ref     : 0
% 2.00/1.31  #Sup     : 18
% 2.00/1.31  #Fact    : 0
% 2.00/1.31  #Define  : 0
% 2.00/1.31  #Split   : 3
% 2.00/1.31  #Chain   : 0
% 2.00/1.31  #Close   : 0
% 2.00/1.31  
% 2.00/1.31  Ordering : KBO
% 2.00/1.31  
% 2.00/1.31  Simplification rules
% 2.00/1.31  ----------------------
% 2.00/1.31  #Subsume      : 3
% 2.00/1.31  #Demod        : 47
% 2.00/1.31  #Tautology    : 9
% 2.00/1.31  #SimpNegUnit  : 2
% 2.00/1.31  #BackRed      : 14
% 2.00/1.31  
% 2.00/1.31  #Partial instantiations: 0
% 2.00/1.31  #Strategies tried      : 1
% 2.00/1.31  
% 2.00/1.31  Timing (in seconds)
% 2.00/1.31  ----------------------
% 2.00/1.31  Preprocessing        : 0.31
% 2.00/1.31  Parsing              : 0.17
% 2.00/1.31  CNF conversion       : 0.02
% 2.00/1.31  Main loop            : 0.18
% 2.00/1.31  Inferencing          : 0.07
% 2.00/1.31  Reduction            : 0.05
% 2.00/1.31  Demodulation         : 0.04
% 2.00/1.31  BG Simplification    : 0.01
% 2.00/1.31  Subsumption          : 0.02
% 2.00/1.31  Abstraction          : 0.01
% 2.00/1.31  MUC search           : 0.00
% 2.00/1.31  Cooper               : 0.00
% 2.00/1.31  Total                : 0.53
% 2.00/1.31  Index Insertion      : 0.00
% 2.00/1.31  Index Deletion       : 0.00
% 2.00/1.31  Index Matching       : 0.00
% 2.00/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
